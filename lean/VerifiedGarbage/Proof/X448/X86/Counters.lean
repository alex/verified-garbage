import VerifiedGarbage.Proof.X448.X86.Ops

/-!
# X448 on x86 (32-bit): public loop counters

Counters preserve memory and every other register; the zero flag controls loop
termination.
-/

namespace VG.Proof.X448.X86

open VG VG.X86

theorem ofNat_beq_zero {k : Nat} (h : k < 2 ^ 32) : (BitVec.ofNat 32 k == 0) = decide (k = 0) := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
    exact hk this

theorem setCounter_ok (s : State) (k : Nat) (_hk : k < 2 ^ 16) :
    WP isa (.block [.mov .esi (.imm (BitVec.ofNat 32 k))]) s fun t =>
      t.gpr .esi = BitVec.ofNat 32 k ∧ (∀ r, r ≠ .esi → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧
        t.rd = s.rd ∧ t.wr = s.wr := by
  refine wp_mov rfl fun t ht => WP.block_nil ⟨ht.gpr, ht.other, ht.mem, ht.rd, ht.wr⟩


theorem decCounter_ok {s : State} {k : Nat} (hk : k < 2 ^ 16)
    (hb : s.gpr .esi = BitVec.ofNat 32 (k + 1)) :
    WP isa (.block [.alu .sub .esi (.imm 1)]) s fun t =>
      t.gpr .esi = BitVec.ofNat 32 k ∧ (∀ r, r ≠ .esi → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧
        t.rd = s.rd ∧ t.wr = s.wr ∧ t.zf = some (decide (k = 0)) := by
  have he : s.gpr .esi - (1 : BitVec 32) = BitVec.ofNat 32 k := by
    change s.gpr .esi - BitVec.ofNat 32 1 = _
    rw [hb, BitVec.ofNat_add, BitVec.add_sub_cancel]
  refine wp_alu (Or.inr (Or.inl rfl)) rfl fun t ht hz => WP.block_nil
    ⟨ht.gpr.trans he, ht.other, ht.mem, ht.rd, ht.wr, ?_⟩
  rw [hz]
  change some (s.gpr .esi - (1 : BitVec 32) == 0) = _
  rw [he, ofNat_beq_zero (by omega)]

end VG.Proof.X448.X86
