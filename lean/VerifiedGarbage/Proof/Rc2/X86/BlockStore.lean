import VerifiedGarbage.Proof.Rc2.X86.BlockLoad
import VerifiedGarbage.Proof.Rc2.Memory32

/-! # Writing the four RC2 words as little-endian bytes -/

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Rc2.X86 VG.WriteBytes VG.Proof.Rc2.Word32

theorem storeWord_ok (s : State) (i : Nat) (hi : i < 4) (v : BitVec 16)
    (value : s.mem.readW (wordBase s + BitVec.ofNat 64 (4 * i)) 32 = v.setWidth 32)
    (scratchFit : (s.gpr .ebp).toNat + 256 ≤ 2 ^ 32)
    (readable : InRegions (s.rd ++ s.wr) (wordBase s + BitVec.ofNat 64 (4 * i)) 4)
    (fit : (s.gpr .edi).toNat + 8 ≤ 2 ^ 32)
    (writable : ∀ j < 8, InRegions s.wr (addr32 (s.gpr .edi) + BitVec.ofNat 64 j) 1) :
    ∃ s', runBlock isa (storeWord i) s = some s' ∧
      Keep [.eax] {s with
        mem := (s.mem.writeW (addr32 (s.gpr .edi) + BitVec.ofNat 64 (2 * i)) (v.setWidth 8)).writeW
          (addr32 (s.gpr .edi) + BitVec.ofNat 64 (2 * i + 1)) ((v >>> 8).setWidth 8)} s' := by
  have lo := writable (2 * i) (by omega)
  have high := writable (2 * i + 1) (by omega)
  have a := addr_add (x := s.gpr .edi) (k := 2 * i) (by omega)
  have b := addr_add (x := s.gpr .edi) (k := 2 * i + 1) (by omega)
  have c : addr32 (s.gpr .ebp + BitVec.ofNat 32 (wordOff i)) = wordBase s + BitVec.ofNat 64 (4 * i) := by
    rw [addr_add (by simp only [wordOff, Nat.mod_eq_of_lt hi]; omega), wordOff_eq s i hi]
  refine ⟨_, by
    simp (config := {decide := true}) only [storeWord, runBlock_cons, runStep_some, runBlock_nil,
      exec, execShift, readSrc, State.ea, memOp, Reg8.reg, State.load32, State.store8,
      ← addr_eq_def, a, b, c, lo, high, readable, value, ite_true, ite_false,
      Option.map_some, gpr_setReg, gpr_setFlags, mem_setReg, mem_setFlags,
      rd_setReg, rd_setFlags, wr_setReg, wr_setFlags]
    rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_singleton] at hr
    simp only [gpr_setReg, gpr_setFlags, hr, ite_false]
  · simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32)]
    have byte : ((v.setWidth 32) >>> 8).setWidth 8 = (v >>> 8).setWidth 8 := by
      apply BitVec.eq_of_getLsbD_eq
      intro j hj
      simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hj,
        show 8 + j < 32 by omega, decide_true, Bool.true_and]
    rw [byte]
  · rfl
  · rfl

theorem storeWords_ok (n : Nat) (hn : n ≤ 4) (s : State) (v : Spec.Rc2.State) (hv : MemWords s.mem (wordBase s) v)
    (fit : (s.gpr .edi).toNat + 8 ≤ 2 ^ 32)
    (scratchFit : (s.gpr .ebp).toNat + 256 ≤ 2 ^ 32)
    (readable : ∀ i < 4, InRegions (s.rd ++ s.wr) (wordBase s + BitVec.ofNat 64 (4 * i)) 4)
    (sep : (Region.mk (wordBase s) 16).Disjoint ⟨addr32 (s.gpr .edi), 8⟩)
    (writable : ∀ j < 8, InRegions s.wr (addr32 (s.gpr .edi) + BitVec.ofNat 64 j) 1) :
    WP isa (.block ((List.range n).flatMap storeWord)) s (fun s' =>
      Keep [.eax] {s with mem := writeBytes s.mem (addr32 (s.gpr .edi)) (outputBytes v n)} s') := by
  induction n generalizing s with
  | zero =>
    apply WP.block_nil
    exact ⟨fun _ _ => rfl, (writeBytes_nil s.mem (addr32 (s.gpr .edi))).symm, rfl, rfl⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    apply WP.mono (ih (by omega) s hv fit scratchFit readable sep writable)
    intro s₁ keep₁
    have ptr₁ := keep₁.reg .edi (by decide)
    have scratch₁ := keep₁.reg .ebp (by decide)
    have base₁ : wordBase s₁ = wordBase s := by unfold wordBase; rw [scratch₁]
    have frame₁ : Frame [⟨addr32 (s.gpr .edi), 8⟩] s.mem s₁.mem := by
      rw [keep₁.mem]
      exact writeBytes_frame _ _ _ (by
        simpa only [BitVec.add_zero] using Offset.contains_base (addr32 (s.gpr .edi))
          (d := 0) (n := (outputBytes v n).length) (by rw [outputBytes_length]; omega) (by decide))
    have val₁ : s₁.mem.readW (wordBase s₁ + BitVec.ofNat 64 (4 * n)) 32 = (v.getD n 0).setWidth 32 := by
      rw [base₁, frame₁.readW (r := ⟨wordBase s, 16⟩)
        (Offset.contains_base _ (by omega) (by omega)) (by simpa using sep) (by decide)]
      exact hv n (by omega)
    obtain ⟨s₂, run₂, keep₂⟩ := storeWord_ok s₁ n (by omega) _ val₁
      (by rw [scratch₁]; exact scratchFit)
      (by rw [keep₁.rd, keep₁.wr, base₁]; exact readable n (by omega))
      (by rw [ptr₁]; exact fit) (by rw [keep₁.wr, ptr₁]; exact writable)
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
    refine ⟨fun r hr => (keep₂.reg r hr).trans (keep₁.reg r hr), ?_,
      keep₂.rd.trans keep₁.rd, keep₂.wr.trans keep₁.wr⟩
    rw [keep₂.mem, keep₁.mem, ptr₁, outputBytes_write _ _ _ n (by omega)]

theorem blockStore_ok (s : State) (v : Spec.Rc2.State) (hv : MemWords s.mem (wordBase s) v)
    (fit : (s.gpr .edi).toNat + 8 ≤ 2 ^ 32)
    (scratchFit : (s.gpr .ebp).toNat + 256 ≤ 2 ^ 32)
    (readable : ∀ i < 4, InRegions (s.rd ++ s.wr) (wordBase s + BitVec.ofNat 64 (4 * i)) 4)
    (sep : (Region.mk (wordBase s) 16).Disjoint ⟨addr32 (s.gpr .edi), 8⟩)
    (writable : ∀ j < 8, InRegions s.wr (addr32 (s.gpr .edi) + BitVec.ofNat 64 j) 1) :
    WP isa (.block ((List.range 4).flatMap storeWord)) s (fun s' =>
      Keep [.eax] {s with mem := s.mem.writeW (addr32 (s.gpr .edi)) (pack v)} s') := by
  apply WP.mono (storeWords_ok 4 (by decide) s v hv fit scratchFit readable sep writable)
  intro s' h
  rw [outputBytes_pack] at h
  exact h

end VG.Proof.Rc2.X86
