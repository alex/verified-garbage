import VerifiedGarbage.Proof.TripleDes.AArch64.Ecb.Slice
import VerifiedGarbage.Proof.TripleDes.AArch64.Ecb.Steps
import VerifiedGarbage.Proof.TripleDes.EcbMemory

namespace VG.Proof.TripleDes.AArch64.Ecb

open VG VG.AArch64 VG.Spec.TripleDes

structure BodyPost (d : Direction) (s : State) (n : Nat) (s' : State) : Prop where
  ptr : s'.gpr .x1 = s.gpr .x1 + 8
  count : s'.gpr .x23 = BitVec.ofNat 64 (n - 1)
  flag : zeroCount s' = some (decide (n = 1))
  reg : ∀ r ∈ kept, r ≠ .x1 → r ≠ .x23 → s'.gpr r = s.gpr r
  callee : ∀ r ∈ savedAcrossCall, r ≠ .x23 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame ([dataR s, ⟨s.gpr .x2, 512⟩]) s.mem s'.mem
  data : Spec.TripleDes.blockAt s'.mem (s.gpr .x1) =
    blockResult (Spec.TripleDes.scheduleAt s.mem (s.gpr .x0)) d
      (Spec.TripleDes.blockAt s.mem (s.gpr .x1))

theorem body_ok (d : Direction) (s : State) (n : Nat) (hn : 1 ≤ n) (bound : n < 2 ^ 64)
    (count : s.gpr .x23 = BitVec.ofNat 64 n) (hp : StepPre s) :
    WP isa (.seq (Impl.TripleDes.AArch64.Ecb.blockCall d) (.block Impl.TripleDes.AArch64.Ecb.advance)) s (BodyPost d s n) := by
  apply WP.seq
  apply WP.mono (call_ok d s hp.call)
  intro s₁ h₁
  obtain ⟨s₂, run₂, ptr₂, count₂, flag₂, keep₂⟩ := advance_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have count' : s₁.gpr .x23 - 1 = BitVec.ofNat 64 (n - 1) := by
    rw [h₁.reg .x23 (by decide), count]
    exact Offset.ofNat_sub_ofNat hn
  refine ⟨by rw [ptr₂, h₁.reg .x1 (by decide)], count₂.trans count', ?_, ?_, ?_,
    keep₂.rd.trans h₁.rd, keep₂.wr.trans h₁.wr, ?_, ?_⟩
  · rw [flag₂, count']
    rw [counter_zero (n - 1) (by omega)]
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
  · rw [keep₂.mem]; exact h₁.output

theorem BodyPost.tail {d : Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s (n + 1) s') (hp : StepPre s (n + 1)) : StepPre s' n :=
  hp.slice (i := 1) (by omega) h.rd h.wr
    (h.reg .x0 (by decide) (by decide) (by decide))
    (h.reg .x2 (by decide) (by decide) (by decide))
    h.ptr

end VG.Proof.TripleDes.AArch64.Ecb
