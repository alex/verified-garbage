import VerifiedGarbage.Proof.X448.Arm.Ops

/-!
# X448 on ARMv7: public loop counters

Untrusted: everything here is checked by Lean. Counters preserve memory
and every other register; the zero flag controls loop termination.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm
open VG.Proof.X25519.Arm (wp_movw wp_subs op2_imm ofNat_beq_zero)

theorem setCounter_ok (s : State) (k : Nat) (hk : k < 2 ^ 16) :
    WP isa (.block [.movw .r11 (BitVec.ofNat 16 k)]) s fun t =>
      t.gpr .r11 = BitVec.ofNat 32 k ∧ (∀ r, r ≠ .r11 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧
        t.rd = s.rd ∧ t.wr = s.wr := by
  refine wp_movw fun t ht => WP.block_nil ⟨?_, ht.other, ht.mem, ht.rd, ht.wr⟩
  rw [ht.gpr]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hk]

theorem decCounter_ok {s : State} {k : Nat} (hk : k < 2 ^ 16)
    (hb : s.gpr .r11 = BitVec.ofNat 32 (k + 1)) :
    WP isa (.block [.subs .r11 .r11 (.imm 1)]) s fun t =>
      t.gpr .r11 = BitVec.ofNat 32 k ∧ (∀ r, r ≠ .r11 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧
        t.rd = s.rd ∧ t.wr = s.wr ∧ t.z = decide (k = 0) := by
  have he : s.gpr .r11 - (1 : BitVec 32) = BitVec.ofNat 32 k := by
    change s.gpr .r11 - BitVec.ofNat 32 1 = _
    rw [hb, BitVec.ofNat_add, BitVec.add_sub_cancel]
  refine wp_subs (op2_imm (by decide)) fun t ht hz => WP.block_nil
    ⟨ht.gpr.trans he, ht.other, ht.mem, ht.rd, ht.wr, ?_⟩
  rw [hz, he, ofNat_beq_zero (by omega)]

end VG.Proof.X448.Arm
