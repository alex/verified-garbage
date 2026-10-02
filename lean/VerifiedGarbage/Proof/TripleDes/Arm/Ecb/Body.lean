import VerifiedGarbage.Proof.TripleDes.Arm.Ecb.Slice
import VerifiedGarbage.Proof.TripleDes.Arm.Ecb.Steps
import VerifiedGarbage.Proof.TripleDes.EcbMemory

namespace VG.Proof.TripleDes.Arm.Ecb

open VG VG.Arm VG.Spec.TripleDes

structure BodyPost (d : Direction) (s : State) (n : Nat) (s' : State) : Prop where
  ptr : s'.gpr .r1 = s.gpr .r1 + 8
  count : s'.gpr .r3 = BitVec.ofNat 32 (n - 1)
  flag : zeroCount s' = some (decide (n = 1))
  reg : ∀ r ∈ kept, r ≠ .r1 → r ≠ .r3 → s'.gpr r = s.gpr r
  callee : ∀ r ∈ savedAcrossCall, r ≠ .r3 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame ([dataR s, ⟨State.addr (s.gpr .r2), 512⟩]) s.mem s'.mem
  data : Spec.TripleDes.blockAt s'.mem (State.addr (s.gpr .r1)) =
    blockResult (Spec.TripleDes.scheduleAt s.mem (State.addr (s.gpr .r0))) d
      (Spec.TripleDes.blockAt s.mem (State.addr (s.gpr .r1)))

theorem body_ok (d : Direction) (s : State) (n : Nat) (hn : 1 ≤ n) (bound : n < 2 ^ 32)
    (count : s.gpr .r3 = BitVec.ofNat 32 n) (hp : StepPre s) :
    WP isa (.seq (Impl.TripleDes.Arm.Ecb.blockCall d) (.block Impl.TripleDes.Arm.Ecb.advance)) s (BodyPost d s n) := by
  apply WP.seq
  apply WP.mono (call_ok d s hp.call)
  intro s₁ h₁
  obtain ⟨s₂, run₂, ptr₂, count₂, flag₂, keep₂⟩ := advance_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have count' : s₁.gpr .r3 - 1 = BitVec.ofNat 32 (n - 1) := by
    rw [h₁.reg .r3 (by decide), count]
    exact Offset.ofNat_sub_ofNat hn
  refine ⟨by rw [ptr₂, h₁.reg .r1 (by decide)], count₂.trans count', ?_, ?_, ?_,
    keep₂.rd.trans h₁.rd, keep₂.wr.trans h₁.wr, ?_, ?_⟩
  · rw [flag₂, count']
    rw [counter_zero (n - 1) (by omega)]
    have he : n - 1 = 0 ↔ n = 1 := by omega
    simp only [he]
  · intro r hr hs hb
    exact (keep₂.reg r (by simp [hs, hb])).trans (h₁.reg r hr)
  · intro r hr hb
    have hs : r ≠ .r1 := by
      have fact : ∀ r ∈ savedAcrossCall, r ≠ .r1 := by decide
      exact fact r hr
    exact (keep₂.reg r (by simp [hs, hb])).trans (h₁.callee r hr)
  · rw [keep₂.mem]; exact h₁.mem
  · rw [keep₂.mem]; exact h₁.output

theorem BodyPost.tail {d : Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s (n + 1) s') (hp : StepPre s (n + 1)) (hn : 1 ≤ n) : StepPre s' n :=
  hp.slice (i := 1) (by omega) hn h.rd h.wr
    (h.reg .r0 (by decide) (by decide) (by decide))
    (h.reg .r2 (by decide) (by decide) (by decide))
    h.ptr

end VG.Proof.TripleDes.Arm.Ecb
