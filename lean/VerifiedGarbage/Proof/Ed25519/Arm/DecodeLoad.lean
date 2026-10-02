import VerifiedGarbage.Proof.Ed25519.Arm.SplitYSign
import VerifiedGarbage.Proof.Ed25519.Arm.CanonicalY
import VerifiedGarbage.Proof.Ed25519.Bytes

/-! Read canonical y and the encoded sign from the 32 input bytes. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem packedV_decode (m : Mem) (p : Addr) :
    packedV m p = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p 32) := by
  rw [decodeLE_eq]
  exact (leNum_bytesAt2 m p 16).symm

theorem pointDecodeLoad_ok {s : State} {base ptr : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base)
    (hp : s.gpr .r12 = ptr) (hfit : ptr.toNat + 32 ≤ 2 ^ 32)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (State.addr ptr + BitVec.ofNat 64 i) 1)
    (hsep : (⟨State.addr ptr, 32⟩ : Region).Disjoint ⟨State.addr base, 8192⟩) :
    WP isa pointDecodeLoad s fun t => DecodeKeep base s t ∧ AllLim t.mem base ∧
      t.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 =
        BitVec.ofNat 32 (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32) / 2 ^ 255 == 1).toNat ∧
      env t.mem base 1 = VG.Proof.X25519.toFe
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32) % 2 ^ 255) ∧
      t.z = decide (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32) % 2 ^ 255 < Spec.X25519.P) := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (unpackField_ok hc (o := offset 1) (src := 0) (by decide) (by decide) hp
    (by omega) (by simpa only [Nat.zero_add] using hr) ?_) fun u ⟨ur, uf, ul, uv⟩ => ?_
  · have hp0 : State.addr ptr + BitVec.ofNat 64 0 = State.addr ptr := BitVec.add_zero _
    rw [hp0]
    exact hsep.sub_right (Offset.sub_base _ (by decide))
  have vu : V u.mem (State.addr base) (offset 1) =
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32) :=
    uv.trans ((congrArg (packedV s.mem) (BitVec.add_zero _)).trans (packedV_decode _ _))
  obtain ⟨uk, ull, _⟩ := field_finish 1 hl (ur.mono (by decide)) (frame_o uf) ul (v := FS u.mem (State.addr base) (offset 1)) rfl
  refine WP.mono (splitYSign_ok (uk.ctx hc) ull) fun v ⟨vk, vl, vy, vs⟩ => ?_
  have kv : DecodeKeep base s v := (DecodeKeep.of_keep uk).trans vk
  have ve : env v.mem base 1 = VG.Proof.X25519.toFe
      (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32) % 2 ^ 255) :=
    congrArg VG.Proof.X25519.toFe (vy.trans (congrArg (· % 2 ^ 255) vu))
  refine WP.mono (canonicalY_ok (kv.ctx hc) vl) fun t ⟨tk, tl, te, tz⟩ => ?_
  refine ⟨kv.trans (DecodeKeep.of_keep tk), tl, ?_, (congrFun te 1).trans ve, ?_⟩
  · rw [tk.sign, vs, vu]
  · rw [tz, vy, vu]

end VG.Proof.Ed25519.Arm
