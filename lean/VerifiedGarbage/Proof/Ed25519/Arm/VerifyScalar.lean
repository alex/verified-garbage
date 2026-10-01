import VerifiedGarbage.Proof.Ed25519.Arm.VerifyHeaders
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarCodec

/-! Untrusted: the signature's scalar is checked canonically, before point decoding. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem verifyScalar_ok {b pk sig challenge : BitVec 32} {s : State}
    (hc : VerifyContext b pk sig challenge s) :
    WP isa (.block verifyScalar) s fun t => VerifyKeep b s t ∧
      t.z = decide (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr (sig + 32)) 32) < Spec.Ed25519.L) := by
  unfold verifyScalar
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (loadHeader_ok hc.ctx 8132 (by decide)) fun a ⟨ar, am, ap⟩ => ?_
  have ak : VerifyKeep b s a := VerifyKeep.of_rest ar (by decide) am
  refine WP.mono (addInput32_ok a) fun c ⟨cr, cm, cp⟩ => ?_
  have ck : VerifyKeep b s c := ak.trans (VerifyKeep.of_rest cr (by decide) cm)
  have ci := (hc.keep ck).sigInput.suffix32
  have cptr : c.gpr .r12 = sig + 32 := by rw [cp, ap, hc.sigHeader]
  refine WP.mono (unpackField_ok (ck.ctx hc.ctx) (o := SR) (src := 0) (by decide) (by decide)
    cptr (by simpa using ci.fit) (by simpa using ci.readable)
    (by simpa using ci.separate.sub_right (Offset.sub_base _ (by decide : SR + 64 ≤ 8192))))
    fun d ⟨dr, df, dl, dv⟩ => ?_
  have dk : VerifyKeep b s d := ck.trans (VerifyKeep.of_small dr (by decide) df (by decide) (by decide))
  have val : V d.mem (State.addr b) SR =
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr (sig + 32)) 32) := by
    have dv' : V d.mem (State.addr b) SR = packedV c.mem (State.addr (sig + 32)) := by simpa only [BitVec.add_zero] using dv
    rw [dv', ← scalar_packed_decode, (hc.sigInput.suffix32).bytes ck]
  refine WP.mono (scalarCompare_ok (dk.ctx hc.ctx) dl) fun e ⟨er, ef, ev⟩ => ?_
  have ek := dk.trans (VerifyKeep.of_small er (by decide) ef (by decide) (by decide))
  refine wp_cmp (op2_imm (by decide)) fun t ht hz => WP.block_nil ⟨
    ek.trans (VerifyKeep.of_rest (ht.rest []) (by decide) ht.mem), ?_⟩
  rw [hz]
  change decide (e.gpr .r5 - (0 : BitVec 32) = 0) = _
  have es : e.gpr .r5 - (0 : BitVec 32) = e.gpr .r5 := BitVec.sub_zero _
  rw [es]
  have e0 : (e.gpr .r5 = 0) ↔ (e.gpr .r5).toNat = 0 := by
    constructor
    · intro h; rw [h]; rfl
    · intro h; exact BitVec.eq_of_toNat_eq h
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, e0, ev, val]
  split <;> simp_all

end VG.Proof.Ed25519.Arm
