import VerifiedGarbage.Proof.Ed25519.Arm.BatchDigit
import VerifiedGarbage.Proof.Ed25519.Arm.ExpandBits
import VerifiedGarbage.Proof.Ed25519.Arm.AccumulateStep

/-! Untrusted: each expanded digit contains the corresponding scalar bits. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem digit_bit (scalar start i : Nat) (hi : i < 16) :
    ((scalar / 2 ^ start) % 65536 / 2 ^ i) % 2 = (scalarBit scalar (start + i)).toNat := by
  have hp : (65536 : Nat) = 2 ^ i * 2 ^ (16 - i) := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
  rw [scalarBit_nat, hp, Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (show 2 ∣ 2 ^ (16 - i) from Nat.pow_dvd_pow (m := 1) (n := 16 - i) 2 (by omega)),
    Nat.div_div_eq_div_mul, ← Nat.pow_add]

theorem packedLimb_digit (m : Mem) (p : Addr) (n j : Nat) (hj : j < n) :
    packedLimb m p j = val16 (packedLimb m p) n / 2 ^ (16 * j) % 65536 :=
  (val16_div (fun k _ => packedLimb_lt m p k) hj).symm

theorem batchBits_ok {b p : BitVec 32} {s : State} (hc : Ctx b s)
    (n j : Nat) (hj : j < n) (hn : n ≤ 32) (hfit : p.toNat + 2 * n ≤ 2 ^ 32)
    (hp : s.mem.readW (State.addr b + BitVec.ofNat 64 52) 32 = p)
    (hcj : s.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 = BitVec.ofNat 32 j)
    (hr : ∀ i < 2 * n, InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 i) 1) :
    WP isa (.block batchBits) s fun t => Rest [.r2, .r3, .r9, .r12] s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 32, 16⟩] s.mem t.mem ∧
      ∀ i < 16, t.mem (State.addr b + BitVec.ofNat 64 (32 + i)) =
        BitVec.ofNat 8 (scalarBit (val16 (packedLimb s.mem (State.addr p)) n) (16 * j + i)).toNat := by
  unfold batchBits
  rw [WP.block_append_iff]
  refine WP.mono (batchDigit_ok hc n j hj hn hfit hp hcj hr) fun u ⟨ur, um, uv⟩ => ?_
  refine WP.mono (expandBits_ok (hc.of_rest ur (by decide)) _ uv) fun t ⟨tr, tf, tb⟩ => ?_
  refine ⟨(ur.mono (by decide)).trans (tr.mono (by decide)), by rw [← um]; exact tf, fun i hi => ?_⟩
  rw [tb i hi, packedLimb_digit _ _ n j hj, digit_bit _ _ i hi]

end VG.Proof.Ed25519.Arm
