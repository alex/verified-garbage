import VerifiedGarbage.Proof.TripleDes.X86.Ecb.Slice
import VerifiedGarbage.Proof.TripleDes.X86.Ecb.Steps
import VerifiedGarbage.Proof.TripleDes.EcbMemory

namespace VG.Proof.TripleDes.X86.Ecb
open VG VG.X86 VG.Spec.TripleDes
open VG.Proof.Rc2.X86 (addr32)

structure BodyPost (d : Direction) (s : State) (n : Nat) (s' : State) : Prop where
  ptr : s'.gpr .esi = s.gpr .esi + 8
  count : s'.gpr .edi = BitVec.ofNat 32 (n - 1)
  flag : isa.eval .ne s' = some (decide (1 < n))
  reg : ∀ r ∈ kept, r ≠ .esi → r ≠ .edi → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame [dataR s, ⟨addr32 (s.gpr .ebp), 512⟩, below (s.gpr .esp) 16] s.mem s'.mem
  data : Spec.TripleDes.blockAt s'.mem (addr32 (s.gpr .esi)) =
    blockResult (Spec.TripleDes.scheduleAt s.mem (addr32 (s.gpr .ebx))) d
      (Spec.TripleDes.blockAt s.mem (addr32 (s.gpr .esi)))

theorem body_ok (d : Direction) (s : State) (n : Nat) (hn : 1 ≤ n) (bound : n < 2 ^ 32)
    (count : s.gpr .edi = BitVec.ofNat 32 n) (hp : StepPre s) :
    WP isa (.seq (Impl.TripleDes.X86.Ecb.blockCall d) (.block Impl.TripleDes.X86.Ecb.advance)) s
      (BodyPost d s n) := by
  apply WP.seq
  apply WP.mono (call_ok d s hp.call)
  intro s₁ h₁
  obtain ⟨s₂, run₂, ptr₂, count₂, flag₂, keep₂⟩ := advance_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have count' : s₁.gpr .edi - 1 = BitVec.ofNat 32 (n - 1) := by
    rw [h₁.reg .edi (by decide), count]
    exact Offset.ofNat_sub_ofNat hn
  refine ⟨by rw [ptr₂, h₁.reg .esi (by decide)], count₂.trans count', ?_, ?_,
    keep₂.rd.trans h₁.rd, keep₂.wr.trans h₁.wr, ?_, ?_⟩
  · rw [flag₂]
    change some ((s₁.gpr .edi - 1) != (0 : BitVec 32)) = _
    have value : (s₁.gpr .edi).toNat = n := by
      rw [h₁.reg .edi (by decide), count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
    rw [counter_branch _ (by rw [value]; omega_using [hn]), value]
  · intro r hr hs hb
    exact (keep₂.reg r (by simp [hs, hb])).trans (h₁.reg r hr)
  · rw [keep₂.mem]; exact h₁.mem
  · rw [keep₂.mem]; exact h₁.output

theorem BodyPost.tail {d : Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s (n + 1) s') (hp : StepPre s (n + 1)) (hn : 1 ≤ n) : StepPre s' n :=
  hp.slice (i := 1) (by omega) hn h.rd h.wr
    (h.reg .ebx (by decide) (by decide) (by decide))
    (h.reg .ebp (by decide) (by decide) (by decide))
    (h.reg .esp (by decide) (by decide) (by decide)) h.ptr

end VG.Proof.TripleDes.X86.Ecb
