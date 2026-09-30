import VerifiedGarbage.Proof.Ed25519.Arm.VerifyCTBody
import VerifiedGarbage.Proof.Ed25519.Arm.VerifyCTLit

/-! The verifier's ABI wrapper preserves the public input relation. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

private theorem byteMap_inj : ∀ {xs ys : List Byte}, xs.map (·.toNat) = ys.map (·.toNat) → xs = ys
  | [], [], _ => rfl
  | a :: xs, b :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, byteMap_inj h.2]

structure VerifyWrapPublic (m : Mem) (b pk sig challenge : BitVec 32) (s : State) : Prop where
  pre : verifyLocal.pre s
  r0 : s.gpr .r0 = pk
  r1 : s.gpr .r1 = sig
  r2 : s.gpr .r2 = challenge
  r3 : s.gpr .r3 = b
  pkBytes : Spec.Ed25519.bytesAt s.mem (State.addr pk) 32 = Spec.Ed25519.bytesAt m (State.addr pk) 32
  sigBytes : Spec.Ed25519.bytesAt s.mem (State.addr sig) 64 = Spec.Ed25519.bytesAt m (State.addr sig) 64
  challengeBytes : Spec.Ed25519.bytesAt s.mem (State.addr challenge) 64 = Spec.Ed25519.bytesAt m (State.addr challenge) 64

theorem verifySetup_ct (m : Mem) (b pk sig challenge : BitVec 32) :
    CT (fun x y => VerifyWrapPublic m b pk sig challenge x ∧ VerifyWrapPublic m b pk sig challenge y)
      (.block verifySetup) (fun x y => VerifyPublic m b pk sig challenge x ∧ VerifyPublic m b pk sig challenge y) := by
  apply ctBoth
  · apply ctRegs [.r0, .r1, .r2, .r3] _ (by taint_decide)
    intro x y h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.1.r0.trans h.2.r0.symm
    · exact h.1.r1.trans h.2.r1.symm
    · exact h.1.r2.trans h.2.r2.symm
    · exact h.1.r3.trans h.2.r3.symm
  · intro s h
    have hp := VerifyPre.of h.pre
    refine WP.mono (verifySetup_ok hp) fun t ⟨tc, _, _, tf⟩ => ?_
    have tc' : VerifyContext b pk sig challenge t := by rw [h.r0, h.r1, h.r2, h.r3] at tc; exact tc
    have bytes (p : BitVec 32) (n : Nat) (hn : n ≤ 64)
        (hd : (⟨State.addr p, n⟩ : Region).Disjoint ⟨State.addr b, 8192⟩) :
        Spec.Ed25519.bytesAt t.mem (State.addr p) n = Spec.Ed25519.bytesAt s.mem (State.addr p) n := by
      unfold Spec.Ed25519.bytesAt
      refine List.map_congr_left fun i hi => tf.bytes (R := ⟨State.addr p, n⟩)
        (fun r hr => ?_) (by omega : n ≤ 2 ^ 64) (List.mem_range.mp hi)
      rw [List.mem_singleton.mp hr, h.r3]
      exact hd
    exact ⟨tc', (bytes pk 32 (by decide) tc'.pkInput.separate).trans h.pkBytes,
      (bytes sig 64 (by decide) tc'.sigInput.separate).trans h.sigBytes,
      (bytes challenge 64 (by decide) tc'.challengeInput.separate).trans h.challengeBytes⟩

theorem verify_ct_of_body
    (bodyCT : ∀ (m : Mem) (b pk sig challenge : BitVec 32),
      CT (fun s t => VerifyPublic m b pk sig challenge s ∧ VerifyPublic m b pk sig challenge t)
        verifyBody (fun _ _ => True)) :
    ConstantTime isa verifyLocal.pre verifyLocal.pub verifyEquation := by
  have hct (m : Mem) (b pk sig challenge : BitVec 32) :
      CT (fun x y => VerifyWrapPublic m b pk sig challenge x ∧ VerifyWrapPublic m b pk sig challenge y)
        verifyEquation (fun _ _ => True) := by
    have hb := (bodyCT m b pk sig challenge).wpDep (fun x y h => ⟨verifyBody_ok h.1.ctx, verifyBody_ok h.2.ctx⟩)
    have hb' := hb.mono (fun _ _ h => h) (fun x y ⟨_, a, c, h, hx, hy⟩ =>
      And.intro (hx.1.ctx h.1.ctx.ctx).r0 (hy.1.ctx h.2.ctx.ctx).r0)
    refine RelCT.seq (verifySetup_ct m b pk sig challenge) (RelCT.seq hb' ?_)
    apply ctRegs [.r0] _ (by taint_decide)
    intro x y h r hr
    rw [List.mem_singleton] at hr
    subst r
    exact h.1.trans h.2.symm
  intro s t tx ty u v hs ht ⟨_, h0, h1, h2, h3, hbytes⟩ ex ey
  have hb := byteMap_inj hbytes
  obtain ⟨first, last⟩ := List.append_inj' hb (by simp only [bytesAt_length])
  obtain ⟨first, middle⟩ := List.append_inj' first (by simp only [bytesAt_length])
  rw [← h0] at first
  rw [← h1] at middle
  rw [← h2] at last
  exact (hct s.mem (s.gpr .r3) (s.gpr .r0) (s.gpr .r1) (s.gpr .r2) _ _ _ _ _ _
    ⟨⟨hs, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      ⟨ht, h0.symm, h1.symm, h2.symm, h3.symm, first.symm, middle.symm, last.symm⟩⟩ ex ey).1

theorem verify_ct : ConstantTime isa verifyLocal.pre verifyLocal.pub verifyEquation :=
  verify_ct_of_body verifyBody_ct

end VG.Proof.Ed25519.Arm
