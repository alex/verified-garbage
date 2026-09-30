import VerifiedGarbage.Proof.Rc2.X86_64.Cbc.Encrypt
import VerifiedGarbage.Proof.Rc2.X86_64.Cbc.Decrypt
import VerifiedGarbage.Proof.Rc2.X86_64.Cbc.Slice
import VerifiedGarbage.Proof.Rc2.X86_64.KeyLoop

/-! # A CBC loop iteration and its public counter -/

namespace VG.Proof.Rc2.X86_64.Cbc

open VG VG.X86_64 VG.Impl.Rc2.X86_64

theorem step_ok (d : Spec.Rc2.Direction) (s : State) (hp : StepPre s) :
    WP isa (Impl.Rc2.X86_64.Cbc.step d) s (StepPost d s) := by
  cases d
  · exact encryptStep_ok s hp
  · exact decryptStep_ok s hp

structure BodyPost (d : Spec.Rc2.Direction) (s : State) (n : Nat) (s' : State) : Prop where
  ptr : s'.gpr .rsi = s.gpr .rsi + 8
  count : s'.gpr .rbp = BitVec.ofNat 64 (n - 1)
  flag : s'.zf = some (decide (n = 1))
  reg : ∀ r ∈ kept, r ≠ .rsi → r ≠ .rbp → s'.gpr r = s.gpr r
  callee : ∀ r ∈ calleeSaved, r ≠ .rbp → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame (stepWrites s) s.mem s'.mem
  data : Spec.Rc2.blockAt s'.mem (s.gpr .rsi) =
    (Spec.Rc2.cbcStep (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) d
      (Spec.Rc2.blockAt s.mem (s.gpr .rbx)) (Spec.Rc2.blockAt s.mem (s.gpr .rsi))).1
  iv : Spec.Rc2.blockAt s'.mem (s.gpr .rbx) =
    (Spec.Rc2.cbcStep (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) d
      (Spec.Rc2.blockAt s.mem (s.gpr .rbx)) (Spec.Rc2.blockAt s.mem (s.gpr .rsi))).2

theorem body_ok (d : Spec.Rc2.Direction) (s : State) (n : Nat) (hn : 1 ≤ n) (bound : n < 2 ^ 64)
    (count : s.gpr .rbp = BitVec.ofNat 64 n) (hp : StepPre s) :
    WP isa (Impl.Rc2.X86_64.Cbc.body d) s (BodyPost d s n) := by
  rw [Impl.Rc2.X86_64.Cbc.body]
  apply WP.seq
  apply WP.mono (step_ok d s hp)
  intro s₁ h₁
  obtain ⟨s₂, run₂, ptr₂, count₂, flag₂, keep₂⟩ := advance_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have count' : s₁.gpr .rbp - 1 = BitVec.ofNat 64 (n - 1) := by
    rw [h₁.reg .rbp (by decide), count]
    exact Offset.ofNat_sub_ofNat hn
  refine ⟨by rw [ptr₂, h₁.reg .rsi (by decide)], count₂.trans count', ?_, ?_, ?_,
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
    have hs : r ≠ .rsi := by
      have fact : ∀ r ∈ calleeSaved, r ≠ .rsi := by decide
      exact fact r hr
    exact (keep₂.reg r (by simp [hs, hb])).trans (h₁.callee r hr)
  · rw [keep₂.mem]; exact h₁.mem
  · rw [keep₂.mem]; exact h₁.data
  · rw [keep₂.mem]; exact h₁.iv

theorem BodyPost.tail {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s (n + 1) s') (hp : StepPre s (n + 1)) : StepPre s' n :=
  hp.slice (i := 1) (by omega) h.rd h.wr
    (h.reg .rdi (by decide) (by decide) (by decide))
    (h.reg .rbx (by decide) (by decide) (by decide))
    (h.reg .rdx (by decide) (by decide) (by decide))
    (h.reg .rsp (by decide) (by decide) (by decide)) h.ptr

end VG.Proof.Rc2.X86_64.Cbc
