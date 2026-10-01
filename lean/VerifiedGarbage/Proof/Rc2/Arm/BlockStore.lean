import VerifiedGarbage.Proof.Rc2.Arm.BlockIO
import VerifiedGarbage.Proof.Rc2.Memory32

/-! # Writing the four RC2 words as little-endian bytes -/

namespace VG.Proof.Rc2.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc2.Arm VG.WriteBytes VG.Proof.Rc2.Word32

theorem storeWord_ok (s : State) (i : Nat) (hi : i < 4) (v : BitVec 16)
    (value : s.gpr (wordReg i) = v.setWidth 32)
    (fit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32)
    (writable : ∀ j < 8, InRegions s.wr (State.addr (s.gpr .r1) + BitVec.ofNat 64 j) 1) :
    ∃ s', runBlock isa (storeWord i) s = some s' ∧
      Keep [.r12] {s with
        mem := (s.mem.writeW (State.addr (s.gpr .r1) + BitVec.ofNat 64 (2 * i)) (v.setWidth 8)).writeW
          (State.addr (s.gpr .r1) + BitVec.ofNat 64 (2 * i + 1)) ((v >>> 8).setWidth 8)} s' := by
  have sep := wordReg_separate i
  have lo := writable (2 * i) (by omega)
  have high := writable (2 * i + 1) (by omega)
  have a := addr_add (a := s.gpr .r1) (k := 2 * i) (by omega)
  have b := addr_add (a := s.gpr .r1) (k := 2 * i + 1) (by omega)
  have loOff : 2 * i < 4096 := by omega
  have hiOff : 2 * i + 1 < 4096 := by omega
  refine ⟨_, by
    simp (config := {decide := true}) only [storeWord, runBlock_cons, runStep_some, runBlock_nil,
      exec, Op2.eval, State.store8, loOff, hiOff, a, b, lo, high, ite_true,
      Option.map_some, gpr_setReg, mem_setReg, rd_setReg, wr_setReg,
      ite_false]
    rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_singleton] at hr
    exact gpr_setReg_of_ne _ _ hr
  · rw [value]
    simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32)]
    have byte : ((v.setWidth 32) >>> 8).setWidth 8 = (v >>> 8).setWidth 8 := by
      apply BitVec.eq_of_getLsbD_eq
      intro j hj
      simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hj,
        show 8 + j < 32 by omega, decide_true, Bool.true_and]
    rw [byte]
  · rfl
  · rfl

theorem storeWords_ok (n : Nat) (hn : n ≤ 4) (s : State) (v : Spec.Rc2.State) (hv : Words s v)
    (fit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32)
    (writable : ∀ j < 8, InRegions s.wr (State.addr (s.gpr .r1) + BitVec.ofNat 64 j) 1) :
    WP isa (.block ((List.range n).flatMap storeWord)) s (fun s' =>
      Keep [.r12] {s with mem := writeBytes s.mem (State.addr (s.gpr .r1)) (outputBytes v n)} s') := by
  induction n generalizing s with
  | zero =>
    apply WP.block_nil
    exact ⟨fun _ _ => rfl, (writeBytes_nil s.mem (State.addr (s.gpr .r1))).symm, rfl, rfl⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    apply WP.mono (ih (by omega) s hv fit writable)
    intro s₁ keep₁
    have ptr₁ := keep₁.reg .r1 (by decide)
    have val₁ : s₁.gpr (wordReg n) = (v.getD n 0).setWidth 32 :=
      (keep₁.reg _ (by simpa using (wordReg_separate n).1)).trans (hv n (by omega))
    obtain ⟨s₂, run₂, keep₂⟩ := storeWord_ok s₁ n (by omega) _ val₁
      (by rw [ptr₁]; exact fit) (by rw [keep₁.wr, ptr₁]; exact writable)
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
    refine ⟨fun r hr => (keep₂.reg r hr).trans (keep₁.reg r hr), ?_,
      keep₂.rd.trans keep₁.rd, keep₂.wr.trans keep₁.wr⟩
    rw [keep₂.mem, keep₁.mem, ptr₁, outputBytes_write _ _ _ n (by omega)]

theorem blockStore_ok (s : State) (v : Spec.Rc2.State) (hv : Words s v)
    (fit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32)
    (writable : ∀ j < 8, InRegions s.wr (State.addr (s.gpr .r1) + BitVec.ofNat 64 j) 1) :
    WP isa (.block blockStore) s (fun s' =>
      Keep [.r12] {s with mem := s.mem.writeW (State.addr (s.gpr .r1)) (pack v)} s') := by
  apply WP.mono (storeWords_ok 4 (by decide) s v hv fit writable)
  intro s' h
  rw [outputBytes_pack] at h
  exact h

end VG.Proof.Rc2.Arm
