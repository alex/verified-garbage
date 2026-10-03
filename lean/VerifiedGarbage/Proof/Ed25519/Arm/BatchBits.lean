import VerifiedGarbage.Impl.Ed25519.Arm.BatchBits
import VerifiedGarbage.Proof.Ed25519.Arm.UnpackField
import VerifiedGarbage.Proof.Ed25519.Arm.Packed
import VerifiedGarbage.Proof.Ed25519.Arm.AccumulateStep

/-! Merged from `Proof.Ed25519.Arm.BatchDigit`. -/
section
/-! Read the public-indexed sixteen-bit scalar digit. -/
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
end

/-! Merged from `Proof.Ed25519.Arm.ExpandBits`. -/
section
/-! Expansion of one scalar digit, with an exact sixteen-byte frame. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

structure ExpandInv (b : BitVec 32) (word : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  rest : Rest [.r3, .r9] s₀ s
  frame : Frame [⟨State.addr b + BitVec.ofNat 64 32, k⟩] s₀.mem s.mem
  value : (s.gpr .r3).toNat = word / 2 ^ k
  bits : ∀ i < k, s.mem (State.addr b + BitVec.ofNat 64 (32 + i)) =
    BitVec.ofNat 8 ((word / 2 ^ i) % 2)

theorem expandBits_ok {b : BitVec 32} {s₀ : State} (hc : Ctx b s₀)
    (word : Nat) (hw : (s₀.gpr .r3).toNat = word) :
    WP isa (.block expandBits) s₀ fun t => Rest [.r3, .r9] s₀ t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 32, 16⟩] s₀.mem t.mem ∧
      ∀ i < 16, t.mem (State.addr b + BitVec.ofNat 64 (32 + i)) =
        BitVec.ofNat 8 ((word / 2 ^ i) % 2) := by
  refine WP.mono (wp_range_flatMap (M := isa) (ExpandInv b word s₀)
    (fun k s hk h => ?_) 16 (Nat.le_refl _) s₀
    ⟨Rest.refl _ _, Frame.refl _ _, by simpa only [Nat.pow_zero, Nat.div_one] using hw,
      fun _ hi => by omega⟩) fun t ht => ⟨ht.rest, ht.frame, ht.bits⟩
  have hs := hc.of_rest h.rest (by decide)
  unfold expandBit
  refine wp_dp (op2_imm (by decide)) fun s1 u1 => ?_
  have e1 : (s1.gpr .r9).toNat = (word / 2 ^ k) % 2 := by
    rw [u1.gpr]
    change (s.gpr .r3 &&& (1 : BitVec 32)).toNat = _
    rw [BitVec.toNat_and, show (1 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod, h.value]
  refine wp_strb (a := State.addr b + BitVec.ofNat 64 (32 + k)) (by omega)
    (by rw [u1.other _ (by decide)]; exact hs.ea (by omega))
    (by rw [u1.wr]; exact hs.inW (by omega)) fun s2 u2 =>
    wp_mov (op2_lsr (by decide)) fun t ht => WP.block_nil ?_
  have hm : t.mem = s.mem.writeW (State.addr b + BitVec.ofNat 64 (32 + k)) ((s1.gpr .r9).setWidth 8) := by
    rw [ht.mem, u2.mem, u1.mem]
  refine ⟨h.rest.trans ((u1.rest (by decide)).trans ((u2.rest _).trans (ht.rest (by decide)))),
    ?_, ?_, fun i hi => ?_⟩
  · rw [hm]
    refine (h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩).writeW
      (List.mem_singleton_self _) _ ?_
    exact Offset.contains (State.addr b) (d := 32 + k) (n := 1) (e := 32) (k := k + 1)
      (by omega) (by omega) (by omega)
  · rw [ht.gpr]
    change (s2.gpr .r3 >>> 1).toNat = _
    rw [toNat_shr, u2.gpr, u1.other _ (by decide), h.value, Nat.div_div_eq_div_mul]
    simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
  · rw [hm, VG.WriteBytes.writeW8_apply]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [ite_eq_right (Offset.add_ofNat_ne _ (by omega) (by omega) (by omega))]
      exact h.bits i hi
    · rw [ite_eq_left rfl]; exact byte_eq e1

end VG.Proof.Ed25519.Arm
end

/-! Each expanded digit contains the corresponding scalar bits. -/
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
