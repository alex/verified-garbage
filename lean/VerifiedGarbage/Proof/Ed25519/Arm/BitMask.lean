import VerifiedGarbage.Impl.Ed25519.Arm.PointAccumulate
import VerifiedGarbage.Proof.Ed25519.Arm.AccKeep

/-! Untrusted: scalar bits in the sixteen-byte batch buffer. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem AccKeep.bit {b : BitVec 32} {s t : State} (h : AccKeep b s t) (j : Nat) (hj : j < 16) :
    t.mem (State.addr b + BitVec.ofNat 64 (32 + j)) = s.mem (State.addr b + BitVec.ofNat 64 (32 + j)) := by
  refine h.frame _ fun r hr => ?_
  rw [List.mem_singleton.mp hr]
  exact (Offset.disjoint (State.addr b) (d := 32 + j) (n := 1) (e := 64) (k := 1536)
    (.inl (by omega)) (by omega) (by decide)) _ (Region.contains_self _ _)


theorem scalarBitMask_ok {b : BitVec 32} {s : State} (hc : Ctx b s) (j : Nat) (hj : j < 16)
    (h11 : s.gpr .r11 = BitVec.ofNat 32 j) (bit : Bool)
    (hbit : s.mem (State.addr b + BitVec.ofNat 64 (32 + j)) = BitVec.ofNat 8 bit.toNat) :
    WP isa (.block scalarBitMask) s fun t => AccKeep b s t ∧ t.mem = s.mem ∧
      t.gpr .r9 = 0 - BitVec.ofNat 32 (!bit).toNat := by
  refine wp_dp (op2_reg _ _) fun s1 u1 => ?_
  have ep : s1.gpr .r2 = b + BitVec.ofNat 32 j := by
    rw [u1.gpr]
    change s.gpr .r0 + s.gpr .r11 = _
    rw [hc.r0, h11]
  refine wp_ldrb (a := State.addr b + BitVec.ofNat 64 (32 + j)) (by decide)
    (by rw [ep, Offset.add_add, addr_add (by have := hc.fit; omega)]; rw [Nat.add_comm j 32])
    (by rw [u1.rd, u1.wr]; exact hc.inR (by omega)) fun s2 u2 =>
    wp_dp (op2_imm (by decide)) fun s3 u3 => WP.block_nil ?_
  have hr : Rest [.r2, .r9] s s3 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide)))
  have hm : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  refine ⟨AccKeep.of_rest hr (by decide) hm, hm, ?_⟩
  rw [u3.gpr]
  change s2.gpr .r9 - 1 = _
  rw [u2.gpr, u1.mem, hbit]
  cases bit <;> decide

end VG.Proof.Ed25519.Arm
