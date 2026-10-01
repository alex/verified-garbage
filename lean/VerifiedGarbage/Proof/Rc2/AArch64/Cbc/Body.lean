import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Encrypt
import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Decrypt
import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Slice
import VerifiedGarbage.Proof.Rc2.AArch64.KeyLoop

/-! # A CBC loop iteration and its public counter -/

namespace VG.Proof.Rc2.AArch64.Cbc

open VG VG.AArch64 VG.Impl.Rc2.AArch64

theorem step_ok (d : Spec.Rc2.Direction) (s : State) (hp : StepPre s) :
    WP isa (Impl.Rc2.AArch64.Cbc.step d) s (StepPost d s) := by
  cases d
  · exact encryptStep_ok s hp
  · exact decryptStep_ok s hp

structure BodyPost (d : Spec.Rc2.Direction) (s : State) (n : Nat) (s' : State) : Prop where
  ptr : s'.gpr .x1 = s.gpr .x1 + 8
  count : s'.gpr .x24 = BitVec.ofNat 64 (n - 1)
  flag : zeroCount s' = some (decide (n = 1))
  reg : ∀ r ∈ kept, r ≠ .x1 → r ≠ .x24 → s'.gpr r = s.gpr r
  callee : ∀ r ∈ savedAcrossCall, r ≠ .x24 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame (stepWrites s) s.mem s'.mem
  data : Spec.Rc2.blockAt s'.mem (s.gpr .x1) =
    (Spec.Rc2.cbcStep (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) d
      (Spec.Rc2.blockAt s.mem (s.gpr .x23)) (Spec.Rc2.blockAt s.mem (s.gpr .x1))).1
  iv : Spec.Rc2.blockAt s'.mem (s.gpr .x23) =
    (Spec.Rc2.cbcStep (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) d
      (Spec.Rc2.blockAt s.mem (s.gpr .x23)) (Spec.Rc2.blockAt s.mem (s.gpr .x1))).2

theorem body_ok (d : Spec.Rc2.Direction) (s : State) (n : Nat) (hn : 1 ≤ n) (bound : n < 2 ^ 64)
    (count : s.gpr .x24 = BitVec.ofNat 64 n) (hp : StepPre s) :
    WP isa (Impl.Rc2.AArch64.Cbc.body d) s (BodyPost d s n) := by
  rw [Impl.Rc2.AArch64.Cbc.body]
  apply WP.seq
  apply WP.mono (step_ok d s hp)
  intro s₁ h₁
  obtain ⟨s₂, run₂, ptr₂, count₂, flag₂, keep₂⟩ := advance_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have count' : s₁.gpr .x24 - 1 = BitVec.ofNat 64 (n - 1) := by
    rw [h₁.reg .x24 (by decide), count]
    exact Offset.ofNat_sub_ofNat hn
  refine ⟨by rw [ptr₂, h₁.reg .x1 (by decide)], count₂.trans count', ?_, ?_, ?_,
    keep₂.rd.trans h₁.rd, keep₂.wr.trans h₁.wr, ?_, ?_, ?_⟩
  · rw [flag₂, count']
    have eqZero := counter_eq (n - 1) 0 (by omega) (by decide)
    simp only [BitVec.sub_zero] at eqZero
    change some (BitVec.ofNat 64 (n - 1) == 0#64) = _
    rw [eqZero]
    have he : n - 1 = 0 ↔ n = 1 := by omega
    simp only [he]
  · intro r hr hs hb
    exact (keep₂.reg r (by simp [hs, hb])).trans (h₁.reg r hr)
  · intro r hr hb
    have hs : r ≠ .x1 := by
      have fact : ∀ r ∈ savedAcrossCall, r ≠ .x1 := by decide
      exact fact r hr
    exact (keep₂.reg r (by simp [hs, hb])).trans (h₁.callee r hr)
  · rw [keep₂.mem]; exact h₁.mem
  · rw [keep₂.mem]; exact h₁.data
  · rw [keep₂.mem]; exact h₁.iv

theorem BodyPost.tail {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s (n + 1) s') (hp : StepPre s (n + 1)) : StepPre s' n :=
  hp.slice (i := 1) (by omega) h.rd h.wr
    (h.reg .x0 (by decide) (by decide) (by decide))
    (h.reg .x23 (by decide) (by decide) (by decide))
    (h.reg .x2 (by decide) (by decide) (by decide))
    h.ptr

end VG.Proof.Rc2.AArch64.Cbc
