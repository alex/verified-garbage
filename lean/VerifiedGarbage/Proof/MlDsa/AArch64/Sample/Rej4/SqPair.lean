import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SqFrame

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3 (iterF iterF_succ)

theorem phasePair_ok (sha3 : Bool) {σ s : State} (hp : Pre σ) {n p : Nat} (hn : n < 6) (hpn : p < 2)
    (h : Phase σ n p s) :
    WP isa (Impl.Sha3.AArch64.Neon.Pair.progWith sha3 (pReg p) (bReg (2*p)) (bReg (2*p+1))) s
      (Phase σ n (p+1)) := by
  have hpair := h.states p hpn
  simp only [Nat.lt_irrefl,ite_false,Nat.add_zero] at hpair
  refine WP.mono (pairBlock_ok sha3 hp h.env hpn hn (phase_state_ptr h hpn)
    (h.ptrs (2*p) (by omega)) (h.ptrs (2*p+1) (by omega)) hpair)
    fun t ⟨he,ht,hpt,hat,hbt,hft⟩ => ?_
  rw [← iterF_succ,← iterF_succ] at hpt
  rw [← iterF_succ] at hat hbt
  refine ⟨he,(ht.gpr .x22 (by decide) (by decide) (by decide)).trans h.x22,
    (ht.gpr .x23 (by decide) (by decide) (by decide)).trans h.x23,
    fun k hk => ?_,by rw [ht.gpr .x28 (by decide) (by decide) (by decide)]; exact h.count,
    fun i hi => ?_,fun k hk j hj => ?_⟩
  · obtain ⟨h6,h7,h16⟩ := b_regs k hk
    exact (ht.gpr (bReg k) h6 h7 h16).trans (h.ptrs k hk)
  · by_cases heq : i = p
    · subst i
      simpa only [Nat.lt_succ_self,ite_true] using hpt
    · apply pair_frame hpn hn hi heq hft
      have hs := h.states i hi
      by_cases hc : i < p <;> simpa (disch := omega) only [ite_eq_left,ite_eq_right] using hs
  · have hjnext : j < 168*(n+1) := by split at hj <;> omega
    have hj1008 : j < 1008 := by omega
    by_cases hjold : j < 168*n
    · rw [old_byte hpn hn hk hj1008 (.inl hjold) hft]
      exact h.out k hk j (by split <;> omega)
    · by_cases heq : k = 2*p
      · subst k
        rw [buf_byte_address σ (2*p) n j (by omega),hat.byte (j := j-168*n) (by omega),
          ← F_block σ (2*p) (n := n) (j := j-168*n) hn (by omega),show 168*n+(j-168*n) = j by omega]
      · by_cases heq' : k = 2*p+1
        · subst k
          rw [buf_byte_address σ (2*p+1) n j (by omega),hbt.byte (j := j-168*n) (by omega),
            ← F_block σ (2*p+1) (n := n) (j := j-168*n) hn (by omega),show 168*n+(j-168*n) = j by omega]
        · rw [old_byte hpn hn hk hj1008 (.inr ⟨heq,heq'⟩) hft]
          apply h.out k hk j
          by_cases hc : k < 2*p <;>
            simpa (disch := omega) only [ite_eq_left,ite_eq_right] using hj
end VG.Proof.MlDsa.AArch64.Sample.Rej4
