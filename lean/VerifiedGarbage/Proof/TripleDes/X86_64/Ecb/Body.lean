import VerifiedGarbage.Proof.TripleDes.X86_64.Ecb.Slice
import VerifiedGarbage.Proof.TripleDes.X86_64.Ecb.Steps
import VerifiedGarbage.Proof.TripleDes.EcbMemory

namespace VG.Proof.TripleDes.X86_64.Ecb

open VG VG.X86_64 VG.Spec.TripleDes

structure BodyPost (d : Direction) (s : State) (n : Nat) (s' : State) : Prop where
  ptr : s'.gpr .rsi = s.gpr .rsi + 8
  count : s'.gpr .rbp = BitVec.ofNat 64 (n - 1)
  flag : s'.zf = some (decide (n = 1))
  reg : ∀ r ∈ kept, r ≠ .rsi → r ≠ .rbp → s'.gpr r = s.gpr r
  callee : ∀ r ∈ calleeSaved, r ≠ .rbp → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame ([dataR s, ⟨s.gpr .rdx, 512⟩, stackR s]) s.mem s'.mem
  data : Spec.TripleDes.blockAt s'.mem (s.gpr .rsi) =
    blockResult (Spec.TripleDes.scheduleAt s.mem (s.gpr .rdi)) d
      (Spec.TripleDes.blockAt s.mem (s.gpr .rsi))

theorem body_ok (d : Direction) (s : State) (n : Nat) (hn : 1 ≤ n) (bound : n < 2 ^ 64)
    (count : s.gpr .rbp = BitVec.ofNat 64 n) (hp : StepPre s) :
    WP isa (.seq (Impl.TripleDes.X86_64.Ecb.blockCall d) (.block Impl.TripleDes.X86_64.Ecb.advance)) s (BodyPost d s n) := by
  apply WP.seq
  apply WP.mono (call_ok d s hp.call)
  intro s₁ h₁
  obtain ⟨s₂, run₂, ptr₂, count₂, flag₂, keep₂⟩ := advance_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have count' : s₁.gpr .rbp - 1 = BitVec.ofNat 64 (n - 1) := by
    rw [h₁.reg .rbp (by decide), count]
    exact Offset.ofNat_sub_ofNat hn
  refine ⟨by rw [ptr₂, h₁.reg .rsi (by decide)], count₂.trans count', ?_, ?_, ?_,
    keep₂.rd.trans h₁.rd, keep₂.wr.trans h₁.wr, ?_, ?_⟩
  · rw [flag₂, count']
    rw [counter_zero (n - 1) (by omega)]
    have he : n - 1 = 0 ↔ n = 1 := by omega
    simp only [he]
  · intro r hr hs hb
    exact (keep₂.reg r (by simp [hs, hb])).trans (h₁.reg r hr)
  · intro r hr hb
    have hs : r ≠ .rsi := by
      have fact : ∀ r ∈ calleeSaved, r ≠ .rsi := by decide
      exact fact r hr
    exact (keep₂.reg r (by simp [hs, hb])).trans (h₁.callee r hr)
  · rw [keep₂.mem]; exact h₁.mem
  · rw [keep₂.mem]; exact h₁.output

theorem BodyPost.tail {d : Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s (n + 1) s') (hp : StepPre s (n + 1)) : StepPre s' n :=
  hp.slice (i := 1) (by omega) h.rd h.wr
    (h.reg .rdi (by decide) (by decide) (by decide))
    (h.reg .rdx (by decide) (by decide) (by decide))
    (h.reg .rsp (by decide) (by decide) (by decide)) h.ptr

end VG.Proof.TripleDes.X86_64.Ecb
