import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Contract
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Block
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Spill

/-!
# TDEA-CMAC on x86-64: saving and restoring the registers

Each function saves our caller's callee-saved registers to bytes `[48, 96)` of
the scratch buffer (`save`), and restores them from there, through `r15`
(`restore`).
-/

namespace VG.Proof.CmacTripleDes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacTripleDes.X86_64

theorem offset_nat (i : Nat) : BitVec.ofInt 64 (i : Int) = BitVec.ofNat 64 i := rfl

/-- The memory after saving the registers to the scratch buffer at `S`. -/
abbrev savedMem (s : State) (S : Addr) : Mem := Spill.saveMem s.mem S s.gpr saved

theorem saved_bound : ∀ p ∈ saved, 48 ≤ p.2 ∧ p.2 + 8 ≤ 96 := by decide

theorem save_ok (s : State) (sc : Reg)
    (hw : ∀ d, 48 ≤ d → d + 8 ≤ 96 → InRegions s.wr (s.gpr sc + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa (save sc) s = some s' ∧ s'.gpr = s.gpr ∧ s'.mem = savedMem s (s.gpr sc) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨_, Spill.save_run sc saved s fun p hp => hw p.2 (saved_bound p hp).1 (saved_bound p hp).2, rfl, rfl,
    rfl, rfl⟩

theorem readW_writeW_other (m : Mem) (b : Addr) {d e : Nat} (v : BitVec 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d)
    (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
    (m.writeW (b + BitVec.ofNat 64 e) v).readW (b + BitVec.ofNat 64 d) 64 = m.readW (b + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (Offset.sep b h hd he) (by decide)

/-- The saved registers, read back. -/
theorem savedMem_read (s : State) (S : Addr) :
    (savedMem s S).readW (S + BitVec.ofNat 64 48) 64 = s.gpr .rbx ∧
    (savedMem s S).readW (S + BitVec.ofNat 64 56) 64 = s.gpr .rbp ∧
    (savedMem s S).readW (S + BitVec.ofNat 64 64) 64 = s.gpr .r12 ∧
    (savedMem s S).readW (S + BitVec.ofNat 64 72) 64 = s.gpr .r13 ∧
    (savedMem s S).readW (S + BitVec.ofNat 64 80) 64 = s.gpr .r14 ∧
    (savedMem s S).readW (S + BitVec.ofNat 64 88) 64 = s.gpr .r15 :=
  have h := Spill.saveMem_saved s.mem S s.gpr saved (by decide)
  ⟨h (.rbx, 48) (by decide), h (.rbp, 56) (by decide), h (.r12, 64) (by decide), h (.r13, 72) (by decide),
    h (.r14, 80) (by decide), h (.r15, 88) (by decide)⟩

theorem slot_contains (b : Addr) {d : Nat} (h₁ : 48 ≤ d) (h₂ : d + 8 ≤ 96) :
    (⟨b + BitVec.ofNat 64 48, 48⟩ : Region).Contains (b + BitVec.ofNat 64 d) 8 := by
  rw [show b + BitVec.ofNat 64 d = (b + BitVec.ofNat 64 48) + BitVec.ofNat 64 (d - 48) from
    (Offset.add_add_eq b (by omega)).symm]
  exact Offset.contains_base _ (by omega) (by omega)

/-- Saving the registers changes only their slots. -/
theorem savedMem_frame (s : State) (S : Addr) : Frame [⟨S + BitVec.ofNat 64 48, 48⟩] s.mem (savedMem s S) :=
  Spill.saveMem_frame _ _ _ _ fun p hp => slot_contains _ (saved_bound p hp).1 (saved_bound p hp).2

theorem restore_ok (s : State) {B : Addr} (hb : s.gpr .r15 = B)
    (hr : ∀ d, 48 ≤ d → d + 8 ≤ 96 → InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa restore s = some s' ∧
      s'.gpr .rbx = s.mem.readW (B + BitVec.ofNat 64 48) 64 ∧
      s'.gpr .rbp = s.mem.readW (B + BitVec.ofNat 64 56) 64 ∧
      s'.gpr .r12 = s.mem.readW (B + BitVec.ofNat 64 64) 64 ∧
      s'.gpr .r13 = s.mem.readW (B + BitVec.ofNat 64 72) 64 ∧
      s'.gpr .r14 = s.mem.readW (B + BitVec.ofNat 64 80) 64 ∧
      s'.gpr .r15 = s.mem.readW (B + BitVec.ofNat 64 88) 64 ∧
      s'.gpr .rsp = s.gpr .rsp ∧ s'.mem = s.mem := by
  refine ⟨_, by
    simp (config := {decide := true}) only [restore, saved, List.map, runBlock_cons, runStep_some,
      runBlock_nil, at_, exec, readSrc, State.load64, State.ea, offset_nat, gpr_setReg, mem_setReg,
      rd_setReg, wr_setReg, ite_true, ite_false, Option.map_some, hb,
      hr 48 (by decide) (by decide), hr 56 (by decide) (by decide), hr 64 (by decide) (by decide),
      hr 72 (by decide) (by decide), hr 80 (by decide) (by decide), hr 88 (by decide) (by decide)]
    rfl, ?_⟩
  simp (config := {decide := true}) only [gpr_setReg, mem_setReg, ite_true, ite_false]

/-- The registers restored from slots that have not changed since they
were saved, the stack pointer kept: `gprPreserved`. -/
theorem restored {s₀ s s' : State} {S : Addr} (hm : ∀ d, 48 ≤ d → d + 8 ≤ 96 →
      s.mem.readW (S + BitVec.ofNat 64 d) 64 = (savedMem s₀ S).readW (S + BitVec.ofNat 64 d) 64)
    (h : s'.gpr .rbx = s.mem.readW (S + BitVec.ofNat 64 48) 64 ∧
      s'.gpr .rbp = s.mem.readW (S + BitVec.ofNat 64 56) 64 ∧
      s'.gpr .r12 = s.mem.readW (S + BitVec.ofNat 64 64) 64 ∧
      s'.gpr .r13 = s.mem.readW (S + BitVec.ofNat 64 72) 64 ∧
      s'.gpr .r14 = s.mem.readW (S + BitVec.ofNat 64 80) 64 ∧
      s'.gpr .r15 = s.mem.readW (S + BitVec.ofNat 64 88) 64)
    (hsp : s'.gpr .rsp = s₀.gpr .rsp) : ∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r := by
  obtain ⟨a, b, c, d, e, f⟩ := savedMem_read s₀ S
  obtain ⟨ha, hb, hc, hd, he, hf⟩ := h
  intro r hr
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [ha, hm 48 (by decide) (by decide), a]
  · rw [hb, hm 56 (by decide) (by decide), b]
  · exact hsp
  · rw [hc, hm 64 (by decide) (by decide), c]
  · rw [hd, hm 72 (by decide) (by decide), d]
  · rw [he, hm 80 (by decide) (by decide), e]
  · rw [hf, hm 88 (by decide) (by decide), f]

end VG.Proof.CmacTripleDes.X86_64
