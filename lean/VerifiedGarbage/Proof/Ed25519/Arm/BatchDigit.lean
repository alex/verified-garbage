import VerifiedGarbage.Impl.Ed25519.Arm.BatchBits
import VerifiedGarbage.Proof.Ed25519.Arm.UnpackField

/-! Untrusted: read the public-indexed sixteen-bit scalar digit. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem batchDigit_ok {b p : BitVec 32} {s : State} (hc : Ctx b s)
    (n j : Nat) (hj : j < n) (_hn : n ≤ 32) (hfit : p.toNat + 2 * n ≤ 2 ^ 32)
    (hp : s.mem.readW (State.addr b + BitVec.ofNat 64 52) 32 = p)
    (hcj : s.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 = BitVec.ofNat 32 j)
    (hr : ∀ i < 2 * n, InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 i) 1) :
    WP isa (.block batchDigit) s fun t => Rest [.r2, .r3, .r12] s t ∧ t.mem = s.mem ∧
      (t.gpr .r3).toNat = packedLimb s.mem (State.addr p) j := by
  unfold batchDigit unpackSrc
  simp only [List.cons_append, List.nil_append, Nat.mul_zero, Nat.add_zero]
  refine ldr0_ok hc (by decide) fun s1 u1 =>
    ldr0_ok (hc.of_rest (u1.rest (ws := [.r12]) (by decide)) (by decide)) (by decide) fun s2 u2 =>
    wp_dp (op2_lsl (by decide)) fun s3 u3 => ?_
  have ej : s2.gpr .r2 = BitVec.ofNat 32 j := by rw [u2.gpr, u1.mem]; exact hcj
  have ep : s3.gpr .r12 = p + BitVec.ofNat 32 (2 * j) := by
    rw [u3.gpr]
    change s2.gpr .r12 + (s2.gpr .r2 <<< 1) = _
    rw [u2.other _ (by decide), u1.gpr, hp, ej]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [toNat_shl, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  have r3 : Rest [.r2, .r3, .r12] s s3 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide)))
  have m3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  refine wp_ldrb (a := State.addr p + BitVec.ofNat 64 (2 * j)) (by decide)
    (by
      rw [ep]
      exact (congrArg State.addr (BitVec.add_zero (p + BitVec.ofNat 32 (2 * j)))).trans
        (addr_add (by omega)))
    (by rw [r3.rd, r3.wr]; exact hr _ (by omega)) fun s4 u4 => ?_
  refine wp_ldrb (a := State.addr p + BitVec.ofNat 64 (2 * j + 1)) (by decide)
    (by rw [u4.other _ (by decide), ep, Offset.add_add, addr_add (by omega)])
    (by rw [u4.rd, u4.wr, r3.rd, r3.wr]; exact hr _ (by omega)) fun s5 u5 =>
    wp_dp (op2_lsl (by decide)) fun t ht => WP.block_nil ?_
  have el : (s5.gpr .r3).toNat = byteN s.mem (State.addr p) (2 * j) := by
    rw [u5.other _ (by decide), u4.gpr, m3, toNat_setWidth8]; rfl
  have eh : (s5.gpr .r2 <<< 8).toNat = 256 * byteN s.mem (State.addr p) (2 * j + 1) := by
    rw [u5.gpr, u4.mem, m3, toNat_shl, toNat_setWidth8]
    have := (s.mem (State.addr p + BitVec.ofNat 64 (2 * j + 1))).isLt
    simp only [byteN]
    omega
  refine ⟨r3.trans ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans (ht.rest (by decide)))),
    by rw [ht.mem, u5.mem, u4.mem, m3], ?_⟩
  rw [ht.gpr]
  change (s5.gpr .r3 + (s5.gpr .r2 <<< 8)).toNat = _
  rw [toNat_add_lt (by rw [el, eh]; exact Nat.lt_trans (packedLimb_lt _ _ _) (by decide)), el, eh]
  rfl

end VG.Proof.Ed25519.Arm
