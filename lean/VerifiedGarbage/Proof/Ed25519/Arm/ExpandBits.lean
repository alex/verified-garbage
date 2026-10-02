import VerifiedGarbage.Impl.Ed25519.Arm.BatchBits
import VerifiedGarbage.Proof.Ed25519.Arm.Packed

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
