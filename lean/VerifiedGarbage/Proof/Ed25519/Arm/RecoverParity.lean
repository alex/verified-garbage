import VerifiedGarbage.Impl.Ed25519.Arm.RecoverSign
import VerifiedGarbage.Proof.Ed25519.Arm.FieldCheck
import VerifiedGarbage.Proof.Ed25519.Arm.PointEncode

/-! Sign checks use the canonical x-coordinate and the saved sign bit. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem IKeep.sign {base : BitVec 32} {s t : State} (h : IKeep base s t) :
    t.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 =
      s.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 := by
  apply BitVec.eq_of_toNat_eq
  exact wd_frame h.frame fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)

theorem Keep.sign {base : BitVec 32} {s t : State} (h : Keep base s t) :
    t.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 =
      s.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 := (IKeep.of_keep h).sign

theorem parity_match (x : Nat) (b : Bool) : decide (x % 2 = b.toNat) = ((x % 2 == 1) == b) := by
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> rw [h] <;> cases b <;> decide

theorem recoverParity_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (b : Bool)
    (hl : Lim s.mem (State.addr base) FR)
    (hb : s.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 = BitVec.ofNat 32 b.toNat) :
    WP isa (.block recoverParity) s fun t => Rest [.r2, .r3, .r9] s t ∧ t.mem = s.mem ∧
      t.z = ((V s.mem (State.addr base) FR % 2 == 1) == b) := by
  refine ldr0_ok hc (by decide) fun s1 u1 => wp_dp (op2_imm (by decide)) fun s2 u2 => ?_
  have r2 : Rest [.r2, .r3, .r9] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  refine ldr0_ok (hc.of_rest r2 (by decide)) (by decide) fun s3 u3 =>
    wp_dp (op2_reg _ _) fun s4 u4 => wp_cmp (op2_imm (by decide)) fun t ht hz => WP.block_nil ?_
  have he : (s3.gpr .r9).toNat = V s.mem (State.addr base) FR % 2 := by
    rw [u3.other _ (by decide), u2.gpr]
    change (s1.gpr .r3 &&& (1 : BitVec 32)).toNat = _
    rw [BitVec.toNat_and, show (1 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod, u1.gpr]
    exact (parity_limb hl).symm
  have es : s3.gpr .r2 = BitVec.ofNat 32 b.toNat := by rw [u3.gpr, u2.mem, u1.mem]; exact hb
  refine ⟨r2.trans ((u3.rest (by decide)).trans ((u4.rest (by decide)).trans (ht.rest _))),
    by rw [ht.mem, u4.mem, u3.mem, u2.mem, u1.mem], ?_⟩
  have sub0 : s4.gpr .r9 - (0 : BitVec 32) = s4.gpr .r9 := BitVec.sub_zero _
  rw [hz, sub0, u4.gpr]
  change (s3.gpr .r9 ^^^ s3.gpr .r2 == 0) = _
  rw [← parity_match]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  change (s3.gpr .r9 ^^^ s3.gpr .r2 = 0#32) ↔ _
  rw [BitVec.xor_eq_zero_iff]
  have en : (s3.gpr .r2).toNat = b.toNat := by rw [es, toNat_imm (by cases b <;> decide)]
  constructor
  · intro h
    exact he.symm.trans ((congrArg BitVec.toNat h).trans en)
  · intro h
    exact BitVec.eq_of_toNat_eq (he.trans (h.trans en.symm))

end VG.Proof.Ed25519.Arm
