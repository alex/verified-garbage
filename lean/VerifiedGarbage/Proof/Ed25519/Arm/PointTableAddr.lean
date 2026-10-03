import VerifiedGarbage.Impl.Ed25519.Arm.PointPowers
import VerifiedGarbage.Proof.Ed25519.Arm.PointTableLoad
import VerifiedGarbage.Proof.Ed25519.Arm.PointLoop

/-! Public table addresses and bounded counters. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem movw_nat {v : Nat} (hv : v < 65536) : ((BitVec.ofNat 16 v).setWidth 32).toNat = v := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv,
    Nat.mod_eq_of_lt (by omega)]

theorem tableAddr_ok {s : State} {b : BitVec 32} (hc : Ctx b s) (start j : Nat)
    (ho : start + 128 * j < 8192) (hj : j < 32) (h11 : s.gpr .r11 = BitVec.ofNat 32 j) :
    WP isa (.block (tableAddr start)) s fun t =>
      t.gpr .r12 = b + BitVec.ofNat 32 (start + 128 * j) ∧
      Rest [.r3, .r12] s t ∧ t.mem = s.mem := by
  have hb := hc.fit
  refine wp_movw fun s1 u1 => wp_dp (op2_reg _ _) fun s2 u2 =>
    wp_dp (op2_lsl (by decide)) fun s3 u3 => WP.block_nil ?_
  have e1 : (s1.gpr .r3).toNat = start := by rw [u1.gpr, movw_nat (by omega)]
  have e2 : (s2.gpr .r12).toNat = b.toNat + start := by
    rw [u2.gpr]
    change (s1.gpr .r0 + s1.gpr .r3).toNat = _
    rw [u1.other _ (by decide), hc.r0, toNat_add_lt (by rw [e1]; omega), e1]
  have e11 : (s2.gpr .r11 <<< 7).toNat = 128 * j := by
    rw [u2.other _ (by decide), u1.other _ (by decide), h11, toNat_shl, toNat_imm (by omega)]
    omega
  refine ⟨?_, (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide))),
    by rw [u3.mem, u2.mem, u1.mem]⟩
  apply BitVec.eq_of_toNat_eq
  rw [u3.gpr]
  change (s2.gpr .r12 + (s2.gpr .r11 <<< 7)).toNat = _
  rw [toNat_add_lt (by rw [e2, e11]; omega), e2, e11, hc.ptr_nat ho]
  omega

theorem sub_beq_zero_nat {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    (BitVec.ofNat 32 x - BitVec.ofNat 32 y == 0) = decide (x = y) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, BitVec.sub_eq_iff_eq_add]
  have hz : (0 : BitVec 32) + BitVec.ofNat 32 y = BitVec.ofNat 32 y := BitVec.zero_add _
  rw [hz]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rwa [toNat_imm hx, toNat_imm hy] at this
  · exact congrArg (BitVec.ofNat 32)

theorem powersNext_ok (s : State) (j count : Nat) (hj : j < count) (hn : count ≤ 32)
    (h11 : s.gpr .r11 = BitVec.ofNat 32 j) :
    WP isa (.block (powersNext count)) s fun t =>
      t.gpr .r11 = BitVec.ofNat 32 (j + 1) ∧ t.z = decide (j + 1 = count) ∧
      Rest [.r3, .r11] s t ∧ t.mem = s.mem := by
  refine wp_movw fun s1 u1 => wp_dp (op2_imm (by decide)) fun s2 u2 =>
    wp_cmp (op2_reg _ _) fun s3 u3 hz => WP.block_nil ?_
  have e2 : s2.gpr .r11 = BitVec.ofNat 32 (j + 1) := by
    rw [u2.gpr]
    change s1.gpr .r11 + 1 = _
    rw [u1.other _ (by decide), h11, BitVec.ofNat_add]
    rfl
  have e3 : s2.gpr .r3 = BitVec.ofNat 32 count := by
    rw [u2.other _ (by decide), u1.gpr]
    apply BitVec.eq_of_toNat_eq
    rw [movw_nat (by omega), toNat_imm (by omega)]
  exact ⟨by rw [u3.gpr]; exact e2,
    by rw [hz, e2, e3, sub_beq_zero_nat (by omega) (by omega)],
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest _)),
    by rw [u3.mem, u2.mem, u1.mem]⟩

end VG.Proof.Ed25519.Arm
