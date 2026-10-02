import VerifiedGarbage.Proof.Argon2.X86_64.ParametersSteps

/-! Exact rounded lane length using the verified fixed-time divider. -/

namespace VG.Proof.Argon2.X86_64.Parameters

open VG VG.X86_64 VG.Spec.Argon2

structure Ready (p : Params) (s : State) : Prop where
  memoryRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 176) 8
  lanesRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 184) 8
  memoryWord : s.mem.readW (off (s.gpr .rbp) 176) 64 = BitVec.ofNat 64 p.memory
  lanesWord : s.mem.readW (off (s.gpr .rbp) 184) 64 = BitVec.ofNat 64 p.lanes
  positive : 0 < p.lanes
  memoryBound : p.memory < 2 ^ 32
  lanesBound : p.lanes < 2 ^ 24

def changed : List Reg := [.rdi, .rsi] ++ Divide.changed ++ [.r13]

theorem code_ok (s : State) (p : Params) (h : Ready p s) :
    WP isa Impl.Argon2.X86_64.Parameters.code s fun t =>
      t.gpr .r13 = BitVec.ofNat 64 p.laneLen ∧ Divide.Keeps changed s t := by
  unfold Impl.Argon2.X86_64.Parameters.code
  refine WP.seq ((args_ok s h.memoryRead h.lanesRead).mono ?_)
  rintro a ⟨memory, lanes, ka⟩
  have divisor : a.gpr .rsi = BitVec.ofNat 64 (4 * p.lanes) := by
    rw [lanes, h.lanesWord, show (4 : Addr) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_mul, Nat.mul_comm]
  have n : (a.gpr .rdi).toNat = p.memory := by
    rw [memory, h.memoryWord, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans h.memoryBound (by decide))]
  have bound : 4 * p.lanes < 2 ^ 32 := by have lanesBound := h.lanesBound; omega
  have d : (a.gpr .rsi).toNat = 4 * p.lanes := by
    rw [divisor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans bound (by decide))]
  refine WP.seq ((Divide.code_ok a (by rw [n]; exact h.memoryBound)
    (by rw [d]; have positive := h.positive; omega) (by rw [d]; exact bound)).mono ?_)
  rintro b ⟨quotient, _, kb⟩
  rw [n, d] at quotient
  have word : b.gpr .r9 = BitVec.ofNat 64 (p.memory / (4 * p.lanes)) := by
    rw [← quotient]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine (finish_ok b).mono ?_
  rintro t ⟨value, kt⟩
  refine ⟨?_, (ka.mono (by simp [changed])).trans
    ((kb.mono (by
      intro r hr
      simp only [changed, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      exact Or.inl (Or.inr hr))).trans (kt.mono (by simp [changed])))⟩
  rw [value, word, show (4 : Addr) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_mul,
    Nat.mul_comm, ← Proof.Argon2.laneLen_eq p h.positive]

end VG.Proof.Argon2.X86_64.Parameters
