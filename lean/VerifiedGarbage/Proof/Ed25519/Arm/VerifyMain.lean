import VerifiedGarbage.Proof.Ed25519.Arm.VerifySetup
import VerifiedGarbage.Proof.Ed25519.Arm.VerifyBody
import VerifiedGarbage.Proof.Ed25519.Arm.VerifyFinish

/-! The complete ARM verification equation restores the ABI and returns the specified flag. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem verifyEquation_correct {s : State} (h : VerifyPre s) :
    WP isa verifyEquation s fun t => abiPreserved s t ∧ verifyLocal.post s t := by
  refine WP.seq (WP.mono (verifySetup_ok h) fun u ⟨uc, us, uk, uf⟩ => ?_)
  refine WP.seq (WP.mono (verifyBody_ok uc) fun v ⟨vk, vv⟩ => ?_)
  have vs : ScalarSaved (State.addr (s.gpr .r3)) s.gpr v.mem := us.frame vk.frame fun r hr i hi => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inl (by omega)) (by omega) (by decide)
  refine WP.mono (verifyFinish_ok (vk.ctx uc.ctx) vs) fun t ⟨tg, tk, _, tv⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [tk.sp, vk.rest.sp, uk.sp]⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact tg 0 (by decide)
    · exact tg 1 (by decide)
    · exact tg 2 (by decide)
    · exact tg 3 (by decide)
    · exact tg 4 (by decide)
    · exact tg 5 (by decide)
    · exact tg 6 (by decide)
    · exact tg 7 (by decide)
    · rw [tk.gpr _ (by decide), vk.rest.gpr _ (by decide), uk.gpr _ (by decide)]
  · have bytes (p : BitVec 32) (n : Nat) (hn : n ≤ 64)
        (hd : (⟨State.addr p, n⟩ : Region).Disjoint ⟨State.addr (s.gpr .r3), 8192⟩) :
        Spec.Ed25519.bytesAt u.mem (State.addr p) n = Spec.Ed25519.bytesAt s.mem (State.addr p) n := by
      unfold Spec.Ed25519.bytesAt
      refine List.map_congr_left fun i hi => uf.bytes (R := ⟨State.addr p, n⟩)
        (fun r hr => ?_) (by omega : n ≤ 2 ^ 64) (List.mem_range.mp hi)
      rw [List.mem_singleton.mp hr]
      exact hd
    rw [bytes _ _ (by decide) h.pk_ws, bytes _ _ (by decide) h.sig_ws,
      bytes _ _ (by decide) h.challenge_ws] at vv
    change (t.gpr .r0).toNat = _
    rw [tv, vv]
    cases Spec.Ed25519.verifyEquation
      (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r0)) 32)
      (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) 64)
      (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r2)) 64) <;> rfl

end VG.Proof.Ed25519.Arm
