import VerifiedGarbage.Proof.Ed25519.AArch64.PointMulBatch

/-! Untrusted: checkpoint generation before the batch descent. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem mulCounterInit_ok {s : State} {base : Addr} (hs : Scr s base) (count : Nat) :
    WP isa (.block (mulCounterInit count)) s fun t =>
      t.mem.readW (off base 56) 64 = BitVec.ofNat 64 count ∧
      (∀ r, r ≠ .x8 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Outside base 56 8 s.mem t.mem := by
  rw [mulCounterInit, WP.block_append_iff]
  refine WP.mono (const64_ok s .x8 (BitVec.ofNat 64 count)) fun a ⟨av, ka⟩ => ?_
  apply WP.of_runBlock
  rw [runBlock_cons, store_sc (hs.of_keeps ka (by decide)) (by decide) (by decide), runStep_some, runBlock_nil]
  simp only [Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ka.gpr r (by simpa only [List.mem_singleton] using hr), ka.rd, ka.wr, ka.sp, ?_⟩
  · rw [Mem.readW_writeW_self64]; exact av
  · rw [ka.mem]; exact writeW_outside _ _ _ (by decide)

end VG.Proof.Ed25519.AArch64
