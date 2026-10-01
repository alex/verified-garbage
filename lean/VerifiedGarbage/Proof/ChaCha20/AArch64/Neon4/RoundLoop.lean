import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Setup
import VerifiedGarbage.Proof.ChaCha20.AArch64.Xor

namespace VG.Proof.ChaCha20.AArch64.Neon4

open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Neon4
open VG.Spec.ChaCha20 (innerBlock)

theorem roundCounterInit_ok (s : State) :
    WP isa (.block [.movz .x .x4 10 0]) s fun u =>
      u.gpr .x4 = 10 ∧ u.v = s.v ∧ LoadSame s u := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runBlock_nil, exec,
    Size.bits, ite_true, isa, runStep_some, Option.some.injEq, exists_eq_left']
  exact ⟨RegUpd.gpr_write_self .., rfl,
    ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr, rfl, rfl, rfl, rfl⟩⟩

theorem roundCounterDec_ok (s : State) {n : Nat} (hn : 0 < n ∧ n ≤ 10)
    (hc : s.gpr .x4 = BitVec.ofNat 64 n) :
    WP isa (.block [.subImm .x .x4 .x4 1]) s fun u =>
      u.gpr .x4 = BitVec.ofNat 64 (n - 1) ∧ u.v = s.v ∧ LoadSame s u := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runBlock_nil, exec,
    State.read, Size.bits, ite_true, isa, runStep_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, rfl, ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr, rfl, rfl, rfl, rfl⟩⟩
  rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, hc]
  exact Offset.ofNat_sub_ofNat (by omega)

theorem roundLoop_ok {vs : Nat → CState} {s : State} (h : Holds vs s)
    (ht : s.v .v30 = rol8Table) :
    WP isa roundLoop s fun u =>
      Holds (fun j => Nat.repeat innerBlock 10 (vs j)) u ∧ LoadSame s u := by
  apply WP.seq
  refine (roundCounterInit_ok s).mono fun a ⟨ha, hav, hsa⟩ => ?_
  let Inv : Nat → State → Prop := fun n u =>
    0 < n ∧ n ≤ 10 ∧ u.gpr .x4 = BitVec.ofNat 64 n ∧
    Holds (fun j => Nat.repeat innerBlock (10 - n) (vs j)) u ∧
    u.v .v30 = rol8Table ∧ LoadSame s u
  refine WP.loop (M := isa) Inv ?_ 10 a ?_
  · intro n u ⟨hn, hle, hc, hu, hut, hsu⟩
    apply WP.seq
    refine (doubleRound_ok hu hut).mono fun b ⟨hb, hub⟩ => ?_
    have hcb : b.gpr .x4 = BitVec.ofNat 64 n := by rw [hub.gpr]; exact hc
    refine (roundCounterDec_ok b ⟨hn, hle⟩ hcb).mono fun c ⟨hcc, hcv, hbc⟩ => ?_
    have hsc : LoadSame s c := (hsu.trans
      ⟨fun r _ => congrFun hub.gpr r, hub.mem, hub.rd, hub.wr, hub.sp⟩).trans hbc
    have hcH : Holds (fun j => Nat.repeat innerBlock (10 - (n - 1)) (vs j)) c := by
      have he : 10 - (n - 1) = (10 - n) + 1 := by omega
      rw [he]
      simpa only [Holds, hcv, Nat.repeat] using hb
    have hct : c.v .v30 = rol8Table := by rw [hcv, hub.v30, hut]
    have heval := Xor.eval_nonzero_ofNat c .x4 (by omega : n - 1 < 2 ^ 64) hcc
    by_cases hz : n = 1
    · left
      refine ⟨?_, ?_, hsc⟩
      · simpa only [hz, Nat.sub_self, ne_eq, not_true_eq_false, decide_false] using heval
      · simpa only [hz, Nat.sub_self, Nat.sub_zero] using hcH
    · right
      refine ⟨?_, n - 1, by omega, by omega, by omega, hcc, hcH, hct, hsc⟩
      simpa only [decide_eq_true (by omega : n - 1 ≠ 0)] using heval
  · refine ⟨by decide, by decide, ha, ?_, ?_, hsa⟩
    · simpa only [Holds, hav, Nat.sub_self, Nat.repeat] using h
    · rw [hav, ht]

end VG.Proof.ChaCha20.AArch64.Neon4
